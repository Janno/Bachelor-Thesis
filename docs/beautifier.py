#!/usr/bin/python

if __name__=='__main__':
    from sys import argv, stderr
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(file(argv[1]).read())

    sections = []

    for sect in soup.html.find_all("span", type="keyword", recursive=True):
        if (sect.text == "Section"):
            t = soup.new_tag('section')
            t.attrs['class'] = 'beautiful_section'
            t.string = "start_section"
            sect.parent.insert_before(t)
            sections.append(sect.next_sibling.next_sibling.attrs['name'])
        if (sect.text == "End"):
            t = soup.new_tag('section')
            t.string = "end_section"
            sect.parent.insert_after(t)

    for doc in soup.html.find_all("div", {'class': 'doc'}):
        doc.attrs['class'] = 'doc doc_inner'
        t = soup.new_tag('div')
        t.attrs['class'] = 'doc_outer'
        doc.insert_before(t)
        t.append(doc.extract())

    style = soup.new_tag('style')
    style.string = """
    .beautiful_section {
        padding-left: 10px;
        border-left: 3px solid #90BDFF;
        margin-bottom: 10px;
    }
    .doc_inner {
        background-color: transparent !important;
    }
    .doc_outer {
        background-color: #90BDFF;
        margin-top: 5px;
        margin-bottom: 5px;
    }
    #page-wrap {
      width: 100%;
      margin: 15px auto;
      position: relative;
    }

    #sidebar {
        width: 250px;
        position: fixed;
        right: 15px;
        margin-left: 500px;
        border: 2px solid #FFBD90;
        background-color: white;
        padding: 5px;
        font-family: sans-serif;
        text-overflow: ellipsis;
        overflow-x: hidden;
    }
    #sidebar a {
        font-size: 120%;
    }
    #sidebar ol {
        margin-left: -10px;
    }
    """
    soup.head.append(style) 

    soup.html.body.div.div.extract()

    pw = soup.new_tag('div')
    pw.attrs['id'] = 'page-wrap'
    sb = soup.new_tag('div')
    sb.attrs['id'] = 'sidebar'
    ol = soup.new_tag('ol')
    sb.append(ol)

    prefix = []
    elems = [ol]
    for sect in sections:
        path = sect.split('.')
        while len(prefix) >= len(path):
            prefix.pop()
            elems.pop()
        if path[:-1] == prefix:
            a = soup.new_tag('a')
            a.attrs['href']= "#%s" % sect
            a.string = path[-1]
            li = soup.new_tag('li')
            li.append(a)

            ol = soup.new_tag('ol')
            li.append(ol)
            elems[-1].append(li)
            elems.append(ol)
            prefix.append(path[-1])






    pw.append(sb)
    soup.html.body.insert(0, pw)

    
    t = str(soup)
    t = t.replace('start_section</section>', '')
    t = t.replace('<section>end_section', '')
    print t

        

    
    

